import { connect } from 'react-redux'
import Given from '../../components/Given'
import { addGiven, completeGivenEntry } from '../../actions'

const mapStateToProps = (state) => (
  {
    given: state.given.map(i => state.proof[i]),
    complete: state.givenEntryComplete || false
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onFinishClick: () => dispatch(completeGivenEntry())
  }
)

const RGiven = connect(
  mapStateToProps,
  mapDispatchToProps
)(Given)

export default RGiven

