import { connect } from 'react-redux'
import { getValues } from 'redux-form'
import Given from '../../components/Given'
import { addGiven, completeGivenEntry, toggleLine } from '../../actions'
import { ASSERT_JUSTIFICATION_TYPE } from '../../constants'

const mapStateToProps = (state) => {

  const form = getValues(state.form.addProofLine)
  const selectable = 
    state.proofStepType == "ASSERT" &&
    form && 
    form.justification == ASSERT_JUSTIFICATION_TYPE.IMPLICATION

  return {
    given: state.given.map(i => state.proof[i]),
    complete: state.givenEntryComplete || false,
    selectable
  }
}

const mapDispatchToProps = (dispatch) => (
  {
    onFinishClick: () => dispatch(completeGivenEntry()),
    onSelect: (index) => dispatch(toggleLine(index))
  }
)

const RGiven = connect(
  mapStateToProps,
  mapDispatchToProps
)(Given)

export default RGiven

