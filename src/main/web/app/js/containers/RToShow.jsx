import { connect } from 'react-redux'
import { getInductionSchema, toggleProofMode } from '../actions'
import ToShow from '../components/ToShow'

const mapStateToProps = (state) => (
  {
    ...state.toShow,
    mode: state.mode
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onToggleClick: () => dispatch(toggleProofMode())
  }
)

const RToShow = connect(
  mapStateToProps,
  mapDispatchToProps
)(ToShow)

export default RToShow

