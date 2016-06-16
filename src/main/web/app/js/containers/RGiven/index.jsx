import { connect } from 'react-redux'
import Given from '../../components/Given'
import { addGiven, completeGivenEntry, toggleLine } from '../../actions'

const mapStateToProps = (state) => (
  {
    given: state.given.map(i => state.proof[i]),
    complete: state.givenEntryComplete || false,
    selectable: state.proofStepType == "ASSERT"
  }
)

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

